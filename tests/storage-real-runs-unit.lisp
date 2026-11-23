; Executable Layer B/C storage integration unit gate:
; 1. Multi-level (height = 2) allocator-backed run build (fn2-run-build-alloc-page,
;    fn2-run-emit-page-write, fn2-run-commit-page-write) under tight RAM pool/cache
;    pressure (3 x 64 KiB workspaces, 2-row fn2-run-cache < 4 x 64 KiB run pages).
; 2. Pin-protected cache eviction (fn2-pool-query-acquire -> :pinned refusal,
;    cache unchanged; unpinned sweep evicts unpinned rows cleanly).
; 3. Corruption rejection negative controls on nonresident reload:
;    - 1-bit payload corruption -> (:corrupt :bad-hash), cache unchanged;
;    - wrong writer epoch -> :corrupt, cache unchanged;
;    - wrong expected page-kind -> :corrupt, cache unchanged;
;    - 1-bit child page corruption during cursor :miss -> (:corrupt :bad-hash),
;      cache unchanged.
; 4. Authentic nonresident reload & demand-paged lookup/scan equivalence on a
;    2-row fn2-run-cache (matching resident fn2-run-lookup-image / fn2-run-scan-image).
; 5. Live fn2-manifest (:id 10) standalone pack/unpack roundtrip + negative truncation
;    control, sealed :manifest run write/reload/scan, and cold fn2-run-installed
;    reconstruction answering cold lookups without replaying from extent 0.
; 6. Productive checkpoint cut & pin-gated extent retirement (fn2-alloc-cut
;    0 -> 3 -> 4 -> 6, obligation/promised-read refusal, zero-pin reclamation,
;    and extent reuse).
(in-package "ACL2")
(include-book "../books/runs-page-io")
(include-book "../books/runs-manifest-ops")
(include-book "../books/checkpoint-reclaim-step")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-sru-sid* 3)
(defconst *fn2-sru-run-id* 7)
(defconst *fn2-sru-epoch* 2)
(defconst *fn2-sru-limit* 2276)
(defconst *fn2-sru-hash-base* 160)

; Seven 600-octet-line overview entries at fill limit 2,276 pack 3 per leaf page:
; 3 leaf pages (extents 0, 2, 3) + 1 index root page (extent 1) => height = 2, 4 pages.
(defun fn2-sru-wide-entries (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
 (if (zp (- (nfix n) (nfix i)))
     nil
   (let ((k (nfix i)))
    (cons (list 1 (* 2 (+ 1 k)) (+ 1000 k) (* 10 (+ 1 k))
                (make-list 600 :initial-element (+ 65 (mod k 26))))
          (fn2-sru-wide-entries (+ 1 k) n)))))

(defconst *fn2-sru-entries-7* (fn2-sru-wide-entries 0 7))

(defun fn2-sru-nq (g num)
 (declare (xargs :verify-guards nil))
 (list g num 0 0 nil))

(defconst *fn2-sru-queries*
 (list (fn2-sru-nq 1 2)
       (fn2-sru-nq 1 3)
       (fn2-sru-nq 1 8)
       (fn2-sru-nq 1 9)
       (fn2-sru-nq 1 14)
       (fn2-sru-nq 1 15)
       (fn2-sru-nq 0 9)
       (fn2-sru-nq 2 1)))

; ---------------------------------------------------------------------------
; Simulated External Disk Helpers (64 KiB page images keyed by physical unit)

(defun fn2-sru-read-octets-rev (left idx slot gen okind oslot ogen acc fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix left)))
 (if (zp left)
     acc
   (mv-let (code byte) (fn2-pool-read slot gen idx okind oslot ogen fn2-pool)
    (declare (ignore code))
    (fn2-sru-read-octets-rev (- left 1) (+ 1 (nfix idx)) slot gen okind oslot ogen (cons byte acc) fn2-pool))))

(defun fn2-sru-extract-page (slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil))
 (reverse (fn2-sru-read-octets-rev *fn2-run-page-size* 0 slot gen okind oslot ogen nil fn2-pool)))

(defun fn2-sru-write-octets (bytes idx slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (len bytes)))
 (if (atom bytes)
     (mv :ok fn2-pool)
   (mv-let (code fn2-pool) (fn2-pool-write slot gen idx (car bytes) okind oslot ogen fn2-pool)
    (if (eq code :ok)
        (fn2-sru-write-octets (cdr bytes) (+ 1 (nfix idx)) slot gen okind oslot ogen fn2-pool)
      (mv code fn2-pool)))))

(defun fn2-sru-load-disk-page (unit flip-idx disk okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool) :verify-guards nil))
 (b* ((pair (assoc-equal unit disk))
      ((unless (consp pair)) (mv :no-disk-unit 0 0 fn2-run-cache fn2-pool))
      ((mv rcode slot gen fn2-run-cache fn2-pool)
       (fn2-rmo-reserve-pool-page okind oslot ogen fn2-run-cache fn2-pool))
      ((unless (eq rcode :ok)) (mv rcode 0 0 fn2-run-cache fn2-pool))
      ((mv wcode fn2-pool)
       (fn2-sru-write-octets (cdr pair) 0 slot gen okind oslot ogen fn2-pool))
      ((unless (eq wcode :ok)) (mv wcode 0 0 fn2-run-cache fn2-pool))
      ((mv fcode fn2-pool)
       (if (natp flip-idx)
           (mv-let (rc b) (fn2-pool-read slot gen flip-idx okind oslot ogen fn2-pool)
            (if (eq rc :ok)
                (fn2-pool-write slot gen flip-idx (logxor 1 (nfix b)) okind oslot ogen fn2-pool)
              (mv rc fn2-pool)))
         (mv :ok fn2-pool))))
  (mv fcode slot gen fn2-run-cache fn2-pool)))

; ---------------------------------------------------------------------------
; Allocator-Backed Compaction/Sealer Build Loop + Demand-Paged Lookup/Scan

(defconst *fn2-sru-stobjs*
 '(fn2-extents fn2-run-page-writes fn2-run-installed
   fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
   fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
   fn2-fc fn2-fc-context fn2-b3 fn2-digests))

(defmacro fn2-sru-defun (name args body)
 `(defun ,name ,(append args *fn2-sru-stobjs*)
   (declare (xargs :stobjs ,*fn2-sru-stobjs* :verify-guards nil))
   ,body))

(defmacro fn2-sru-mv (&rest vals)
 `(mv ,@vals ,@*fn2-sru-stobjs*))

(fn2-sru-defun fn2-sru-init (pool-pages cache-rows)
 (b* ((fn2-extents (fn2-alloc-init 16 fn2-extents))
      ((mv & fn2-extents) (fn2-alloc-begin-epoch *fn2-sru-epoch* fn2-extents))
      (fn2-run-page-writes (fn2-run-page-writes-init 16 fn2-run-page-writes))
      (fn2-run-installed (fn2-run-installed-init 4 fn2-run-installed))
      (fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds))
      (fn2-run-cursors (fn2-run-cursors-init 1 fn2-run-cursors))
      (fn2-run-paths (fn2-run-paths-init *fn2-run-max-levels* fn2-run-paths))
      (fn2-run-cache (fn2-run-cache-init cache-rows fn2-run-cache))
      (fn2-run-writers (fn2-run-writers-init *fn2-run-max-levels* fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init (* *fn2-run-max-levels* *fn2-run-restart-capacity*) fn2-run-restarts))
      (fn2-fields (fn2-fields-init 1400 fn2-fields))
      (fn2-pool (fn2-pool-init (list (cons pool-pages *fn2-run-page-size*) (cons 4 16384)) 1 2000 fn2-pool))
      (fn2-fc (fn2-fc-init 1 fn2-fc))
      (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-digests (fn2-digests-init 200 fn2-digests)))
  (fn2-sru-mv :ok)))

; One bounded step of allocator-backed run build:
; - :need-page calls fn2-run-build-alloc-page (reserving real extents in fn2-extents);
; - :sealed emits a durable fn2-run-page-writes descriptor + extracts 64 KiB octets to DISK;
; - :promote promotes into l+1 and, on :ok, commits child l's descriptor via fn2-run-commit-page-write;
; - :root commits root l's descriptor via fn2-run-commit-page-write and finishes.
(fn2-sru-defun fn2-sru-build-onestep (layout entries src sgen off next-drow pending disk)
 (b* (((mv code l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-run-build-work 0 4096 fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
  (case code
   (:more
    (fn2-sru-mv nil :more entries off next-drow pending disk))
   (:sealed
    (b* ((drow next-drow)
         (hrow (+ *fn2-sru-hash-base* drow))
         ((mv ecode fn2-digests fn2-run-page-writes)
          (fn2-run-emit-page-write drow hrow 0 l fn2-run-builds fn2-run-writers fn2-digests fn2-run-page-writes))
         ((unless (eq ecode :ok))
          (fn2-sru-mv t (list :emit ecode) entries off next-drow pending disk))
         (unit (fn2-run-page-writes-unit drow fn2-run-page-writes))
         (slot (fn2-run-page-writes-slot drow fn2-run-page-writes))
         (gen (fn2-run-page-writes-gen drow fn2-run-page-writes))
         (octets (fn2-sru-extract-page slot gen 9 0 1 fn2-pool))
         (disk (cons (cons unit octets) disk))
         (pending (put-assoc-equal l drow pending)))
     (fn2-sru-mv nil :more entries off (+ 1 drow) pending disk)))
   (:promote
    (b* (((mv pcode fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)
          (fn2-run-build-promote 0 l fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests))
         ((when (member-eq pcode '(:more :need-page)))
          (fn2-sru-mv nil :more entries off next-drow pending disk))
         ((unless (eq pcode :ok))
          (fn2-sru-mv t (list :promote pcode) entries off next-drow pending disk))
         (drow (cdr (assoc-equal l pending)))
         ((mv ccode fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes)
          (fn2-run-commit-page-write drow 2 *fn2-sru-run-id* 9 0 1
                                     fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
         ((unless (eq ccode :ok))
          (fn2-sru-mv t (list :commit ccode) entries off next-drow pending disk)))
     (fn2-sru-mv nil :more entries off next-drow pending disk)))
   (:root
    (b* ((drow (cdr (assoc-equal l pending)))
         ((mv ccode fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes)
          (fn2-run-commit-page-write drow 2 *fn2-sru-run-id* 9 0 1
                                     fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
         ((unless (eq ccode :ok))
          (fn2-sru-mv t (list :root-commit ccode) entries off next-drow pending disk)))
     (fn2-sru-mv t (list :root l drow) entries off next-drow pending disk)))
   (:need-page
    (b* (((mv acode & & & & & & fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
          (fn2-run-build-alloc-page 0 l fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)))
     (if (eq acode :ok)
         (fn2-sru-mv nil :more entries off next-drow pending disk)
       (fn2-sru-mv t (list :alloc-page acode) entries off next-drow pending disk))))
   (:idle
    (if (consp entries)
        (b* (((mv lcode noff fn2-fields fn2-pool)
              (fn2-run-load-values layout (car entries) *fn2-run-run-entry* src sgen off 9 0 1 fn2-fields fn2-pool))
             ((unless (eq lcode :ok))
              (fn2-sru-mv t (list :load lcode) entries off next-drow pending disk))
             ((mv acode fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
              (fn2-run-build-add 0 *fn2-run-run-entry* fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
         (case acode
          (:ok (fn2-sru-mv nil :more (cdr entries) noff next-drow pending disk))
          (:need-page
           (b* (((mv pcode & & & & & & fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
                 (fn2-run-build-alloc-page 0 0 fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)))
            (if (eq pcode :ok)
                (fn2-sru-mv nil :more entries off next-drow pending disk)
              (fn2-sru-mv t (list :alloc-leaf pcode) entries off next-drow pending disk))))
          (:more (fn2-sru-mv nil :more entries off next-drow pending disk))
          (otherwise (fn2-sru-mv t (list :add acode) entries off next-drow pending disk))))
      (b* (((mv fcode fn2-run-builds) (fn2-run-build-finish 0 fn2-run-builds)))
       (if (eq fcode :ok)
           (fn2-sru-mv nil :more entries off next-drow pending disk)
         (fn2-sru-mv t fcode entries off next-drow pending disk)))))
   (otherwise
    (fn2-sru-mv t (list :work code) entries off next-drow pending disk)))))

(local (in-theory (disable fn2-sru-build-onestep fn2-run-load-values fn2-run-unload-values
                           fn2-run-lookup-step fn2-run-scan-step)))

(defun fn2-sru-build-loop (fuel layout entries src sgen off next-drow pending disk
                           fn2-extents fn2-run-page-writes fn2-run-installed
                           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-extents fn2-run-page-writes fn2-run-installed
                          fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                          fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                 :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel)
     (fn2-sru-mv :fuel next-drow disk)
   (mv-let (done status entries off next-drow pending disk
            fn2-extents fn2-run-page-writes fn2-run-installed
            fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
            fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
            fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-sru-build-onestep layout entries src sgen off next-drow pending disk
                            fn2-extents fn2-run-page-writes fn2-run-installed
                            fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                            fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                            fn2-fc fn2-fc-context fn2-b3 fn2-digests)
    (if done
        (fn2-sru-mv status next-drow disk)
      (fn2-sru-build-loop (- fuel 1) layout entries src sgen off next-drow pending disk
                          fn2-extents fn2-run-page-writes fn2-run-installed
                          fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                          fn2-fc fn2-fc-context fn2-b3 fn2-digests)))))

; Ensure root page (ROOT-UNIT, ROOT-EPOCH, ROOT-ALLOC, ROOT-PKIND, ROOT-HROW)
; is in fn2-run-cache (reloading from DISK via fn2-run-page-reload on miss) and
; start cursor 0.
(fn2-sru-defun fn2-sru-start-cursor-from-disk (sid top-level root-unit root-epoch root-alloc root-pkind root-hrow disk)
 (b* (((mv scode fn2-run-cursors)
       (fn2-run-cursor-start-cached 0 sid top-level root-unit root-alloc
                                    *fn2-run-run-reader* 9 0 1 fn2-run-cursors fn2-run-cache))
      ((when (eq scode :ok))
       (fn2-sru-mv :ok))
      ((unless (eq scode :miss))
       (fn2-sru-mv (list :start scode)))
      ((mv lcode slot gen fn2-run-cache fn2-pool)
       (fn2-sru-load-disk-page root-unit nil disk 9 0 1 fn2-run-cache fn2-pool))
      ((unless (eq lcode :ok))
       (fn2-sru-mv (list :load-root lcode)))
      ((mv rcode detail fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
       (fn2-run-page-reload root-unit root-epoch root-alloc 1 1 root-pkind
                            0 900 950 slot gen root-hrow 9 0 1
                            fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((unless (eq rcode :ok))
       (fn2-sru-mv (list :reload-root rcode detail)))
      ((mv scode2 fn2-run-cursors)
       (fn2-run-cursor-start-cached 0 sid top-level root-unit root-alloc
                                    *fn2-run-run-reader* 9 0 1 fn2-run-cursors fn2-run-cache)))
  (fn2-sru-mv scode2)))

; Resolve a single cursor :miss from DISK via fn2-run-miss-decode + fn2-run-miss-resolve.
(fn2-sru-defun fn2-sru-handle-miss (flip-idx disk)
 (b* (((mv dcode cunit & & & & fn2-fields fn2-digests)
       (fn2-run-miss-decode 0 195 fn2-run-cursors fn2-fields fn2-pool fn2-digests))
      ((unless (eq dcode :ok))
       (fn2-sru-mv dcode :decode))
      ((mv lcode slot gen fn2-run-cache fn2-pool)
       (fn2-sru-load-disk-page cunit flip-idx disk 9 0 1 fn2-run-cache fn2-pool))
      ((unless (eq lcode :ok))
       (fn2-sru-mv lcode :disk))
      ((mv mcode detail fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
       (fn2-run-miss-resolve 0 1 1 0 900 950 slot gen 195 9 0 1
                             fn2-run-cursors fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)))
  (fn2-sru-mv mcode detail)))

(local (in-theory (disable fn2-sru-start-cursor-from-disk fn2-sru-handle-miss)))

; Demand-paged lookup loop: handles :more and :miss transparently.
(defun fn2-sru-paged-lookup-steps (fuel layout disk
                                   fn2-extents fn2-run-page-writes fn2-run-installed
                                   fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                   fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                   fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-extents fn2-run-page-writes fn2-run-installed
                          fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                          fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                 :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel)
     (fn2-sru-mv (list :fuel nil))
   (mv-let (code fn2-run-cursors fn2-run-paths fn2-fields)
     (fn2-run-lookup-step 0 8 *fn2-run-run-query* 10 0 1 fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
    (case code
     (:more
      (fn2-sru-paged-lookup-steps (- fuel 1) layout disk
                                  fn2-extents fn2-run-page-writes fn2-run-installed
                                  fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                  fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                  fn2-fc fn2-fc-context fn2-b3 fn2-digests))
     (:miss
      (mv-let (mcode detail
               fn2-extents fn2-run-page-writes fn2-run-installed
               fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
               fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
               fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-sru-handle-miss nil disk
                             fn2-extents fn2-run-page-writes fn2-run-installed
                             fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                             fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                             fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (if (eq mcode :ok)
           (fn2-sru-paged-lookup-steps (- fuel 1) layout disk
                                       fn2-extents fn2-run-page-writes fn2-run-installed
                                       fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                       fn2-fc fn2-fc-context fn2-b3 fn2-digests)
         (fn2-sru-mv (list (list :miss-fail mcode detail) nil)))))
     (otherwise
      (fn2-sru-mv (list code (if (eq code :found)
                                 (fn2-run-unload-values layout (+ *fn2-run-run-reader* *fn2-run-reader-entry*) fn2-fields fn2-pool)
                               nil))))))))

(local (in-theory (disable fn2-sru-paged-lookup-steps)))

(defun fn2-sru-paged-lookups (qs sid top-level root-unit root-epoch root-alloc root-hrow layout qslot qgen disk
                              fn2-extents fn2-run-page-writes fn2-run-installed
                              fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                              fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                              fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-extents fn2-run-page-writes fn2-run-installed
                          fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                          fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                 :verify-guards nil :measure (len qs)))
 (if (atom qs)
     (fn2-sru-mv nil)
   (b* (((mv & & fn2-fields fn2-pool)
         (fn2-run-load-values layout (car qs) *fn2-run-run-query* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
        ((mv scode
             fn2-extents fn2-run-page-writes fn2-run-installed
             fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
             fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
             fn2-fc fn2-fc-context fn2-b3 fn2-digests)
         (fn2-sru-start-cursor-from-disk sid top-level root-unit root-epoch root-alloc
                                         (if (zp top-level) *page-kind-run-data* *page-kind-run-index*)
                                         root-hrow disk
                                         fn2-extents fn2-run-page-writes fn2-run-installed
                                         fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                         fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                         fn2-fc fn2-fc-context fn2-b3 fn2-digests))
        ((unless (eq scode :ok))
         (fn2-sru-mv (list scode)))
        ((mv one
             fn2-extents fn2-run-page-writes fn2-run-installed
             fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
             fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
             fn2-fc fn2-fc-context fn2-b3 fn2-digests)
         (fn2-sru-paged-lookup-steps 500 layout disk
                                     fn2-extents fn2-run-page-writes fn2-run-installed
                                     fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                     fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                     fn2-fc fn2-fc-context fn2-b3 fn2-digests))
        ((mv rest
             fn2-extents fn2-run-page-writes fn2-run-installed
             fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
             fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
             fn2-fc fn2-fc-context fn2-b3 fn2-digests)
         (fn2-sru-paged-lookups (cdr qs) sid top-level root-unit root-epoch root-alloc root-hrow layout qslot qgen disk
                                fn2-extents fn2-run-page-writes fn2-run-installed
                                fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
    (fn2-sru-mv (cons one rest)))))

; Demand-paged scan loop for overview (sid=3): handles both :miss (reload child
; page) and :lost (ancestor evicted on a 2-row cache -> reload root and re-seek
; strictly after the last delivered (group, number) key!).
(defun fn2-sru-paged-scan-steps (fuel n last-q top-level root-unit root-epoch root-alloc root-hrow qslot qgen disk
                                 fn2-extents fn2-run-page-writes fn2-run-installed
                                 fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                 fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-extents fn2-run-page-writes fn2-run-installed
                          fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                          fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                 :verify-guards nil :measure (nfix fuel)))
 (cond ((zp fuel) (fn2-sru-mv (list :fuel)))
       ((zp n) (fn2-sru-mv (list :count)))
       (t (mv-let (code fn2-run-cursors fn2-run-paths fn2-fields)
            (fn2-run-scan-step 0 8 *fn2-run-run-query* 10 0 1 fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
           (case code
            (:more
             (fn2-sru-paged-scan-steps (- fuel 1) n last-q top-level root-unit root-epoch root-alloc root-hrow qslot qgen disk
                                       fn2-extents fn2-run-page-writes fn2-run-installed
                                       fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                       fn2-fc fn2-fc-context fn2-b3 fn2-digests))
            (:entry
             (let* ((e (fn2-run-unload-values *fn2-overview-entry* (+ *fn2-run-run-reader* *fn2-run-reader-entry*) fn2-fields fn2-pool))
                    (next-q (fn2-sru-nq (nth 0 e) (+ 1 (nfix (nth 1 e))))))
              (mv-let (rest
                       fn2-extents fn2-run-page-writes fn2-run-installed
                       fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                       fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                (fn2-sru-paged-scan-steps (- fuel 1) (- n 1) next-q top-level root-unit root-epoch root-alloc root-hrow qslot qgen disk
                                          fn2-extents fn2-run-page-writes fn2-run-installed
                                          fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                          fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                          fn2-fc fn2-fc-context fn2-b3 fn2-digests)
               (fn2-sru-mv (cons e rest)))))
            (:miss
             (mv-let (mcode detail
                      fn2-extents fn2-run-page-writes fn2-run-installed
                      fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                      fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                      fn2-fc fn2-fc-context fn2-b3 fn2-digests)
               (fn2-sru-handle-miss nil disk
                                    fn2-extents fn2-run-page-writes fn2-run-installed
                                    fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                    fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                    fn2-fc fn2-fc-context fn2-b3 fn2-digests)
              (if (eq mcode :ok)
                  (fn2-sru-paged-scan-steps (- fuel 1) n last-q top-level root-unit root-epoch root-alloc root-hrow qslot qgen disk
                                            fn2-extents fn2-run-page-writes fn2-run-installed
                                            fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                            fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                            fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                (fn2-sru-mv (list (list :miss-fail mcode detail))))))
            (:lost
             (b* (((mv & & fn2-fields fn2-pool)
                   (fn2-run-load-values *fn2-overview-entry* last-q *fn2-run-run-query* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
                  ((mv scode
                       fn2-extents fn2-run-page-writes fn2-run-installed
                       fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                       fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                   (fn2-sru-start-cursor-from-disk *fn2-sru-sid* top-level root-unit root-epoch root-alloc
                                                   (if (zp top-level) *page-kind-run-data* *page-kind-run-index*)
                                                   root-hrow disk
                                                   fn2-extents fn2-run-page-writes fn2-run-installed
                                                   fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                                   fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                                   fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
              (if (eq scode :ok)
                  (fn2-sru-paged-scan-steps (- fuel 1) n last-q top-level root-unit root-epoch root-alloc root-hrow qslot qgen disk
                                            fn2-extents fn2-run-page-writes fn2-run-installed
                                            fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                            fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                            fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                (fn2-sru-mv (list (list :lost-fail scode))))))
            (otherwise
             (fn2-sru-mv (list code))))))))

; Check all N emitted fn2-run-page-writes descriptors and their committed extents.
(defun fn2-sru-check-descriptors (i n fn2-extents fn2-run-page-writes)
 (declare (xargs :stobjs (fn2-extents fn2-run-page-writes) :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
 (if (zp (- (nfix n) (nfix i)))
     t
   (let* ((k (nfix i))
          (ext (fn2-run-page-writes-extent k fn2-run-page-writes))
          (unit (fn2-run-page-writes-unit k fn2-run-page-writes))
          (boff (fn2-run-page-writes-byte-offset k fn2-run-page-writes))
          (ep (fn2-run-page-writes-epoch k fn2-run-page-writes))
          (alloc (fn2-run-page-writes-allocation k fn2-run-page-writes)))
    (and (equal (fn2-run-page-writes-state k fn2-run-page-writes) *fn2-run-page-write-state-committed*)
         (equal unit (fn2-run-extent-unit ext))
         (equal (fn2-run-unit-extent unit) ext)
         (equal boff (fn2-run-extent-byte-offset ext))
         (equal ep *fn2-sru-epoch*)
         (natp alloc)
         (equal (fn2-extents-state ext fn2-extents) *fn2-extent-state-allocated*)
         (equal (fn2-extents-epoch ext fn2-extents) *fn2-sru-epoch*)
         (equal (fn2-extents-counter ext fn2-extents) alloc)
         (fn2-sru-check-descriptors (+ 1 k) n fn2-extents fn2-run-page-writes)))))

(defun fn2-sru-step-nonmore (fuel scanp fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
                 :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel)
     (mv :fuel fn2-run-cursors fn2-run-paths fn2-fields)
   (mv-let (code fn2-run-cursors fn2-run-paths fn2-fields)
     (if scanp
         (fn2-run-scan-step 0 8 *fn2-run-run-query* 10 0 1 fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
       (fn2-run-lookup-step 0 8 *fn2-run-run-query* 10 0 1 fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
    (if (eq code :more)
        (fn2-sru-step-nonmore (- fuel 1) scanp fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
      (mv code fn2-run-cursors fn2-run-paths fn2-fields)))))

(local (in-theory (disable fn2-sru-step-nonmore)))

; ---------------------------------------------------------------------------
; Master Scenario 1: Tight-Pool Allocator-Backed Build, Pin Protection,
; Corruption Rejection, 3-Row Demand-Paged Lookup/Scan & Live Manifest Recovery

(fn2-sru-defun fn2-sru-storage-scenario ()
 (b* (;; Initialize with ONLY 3 x 64 KiB pool workspaces and 3 cache rows
      ;; (< 4-page overview run + 1-page manifest run = 5 x 64 KiB pages!).
      ((mv &
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-init 3 3
                     fn2-extents fn2-run-page-writes fn2-run-installed
                     fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                     fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                     fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv & hslot hgen fn2-pool) (fn2-pool-reserve 1 9 0 1 fn2-pool))
      ((mv & src sgen fn2-pool) (fn2-pool-reserve 1 9 0 1 fn2-pool))
      ((mv & qslot qgen fn2-pool) (fn2-pool-reserve 1 10 0 1 fn2-pool))
      ((mv & mslot mgen fn2-pool) (fn2-pool-reserve 1 9 0 1 fn2-pool))

      ;; 1. Build 7-entry height=2 overview run backed by fn2-extents + simulated disk.
      ((mv start-code fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-run-build-start 0 *fn2-sru-sid* *fn2-sru-run-id* 0 0 136 hslot hgen 0 *fn2-sru-limit*
                            1 1 9 0 1 fn2-run-builds fn2-run-writers fn2-pool))
      ((unless (eq start-code :ok))
       (fn2-sru-mv (list :start-fail start-code)))
      ((mv build-status ndesc disk
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-build-loop 100000 *fn2-overview-entry* *fn2-sru-entries-7* src sgen 0 0 nil nil
                           fn2-extents fn2-run-page-writes fn2-run-installed
                           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                           fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((unless (and (consp build-status) (eq (car build-status) :root)))
       (fn2-sru-mv (list :build-fail build-status)))
      (top-level (cadr build-status))
      (root-drow (caddr build-status))
      (height (+ 1 top-level))
      (entries-built (fn2-run-builds-entries 0 fn2-run-builds))
      (desc-ok (fn2-sru-check-descriptors 0 ndesc fn2-extents fn2-run-page-writes))
      (root-unit (fn2-run-page-writes-unit root-drow fn2-run-page-writes))
      (root-epoch (fn2-run-page-writes-epoch root-drow fn2-run-page-writes))
      (root-alloc (fn2-run-page-writes-allocation root-drow fn2-run-page-writes))
      ((mv xh-code fn2-digests)
       (fn2-run-page-write-extract-hash root-drow 190 fn2-run-page-writes fn2-digests))

      ;; 2. Pin-protection & unpinned eviction controls on cached root page.
      ((mv hit0 rslot0 rgen0) (fn2-run-cache-lookup root-unit root-alloc fn2-run-cache))
      ((mv pin-acq fn2-pool) (fn2-pool-query-acquire rslot0 rgen0 0 64 9 0 1 fn2-pool))
      (pinned-now (fn2-run-cache-pinned-p rslot0 fn2-pool))
      ((mv evict-pinned fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-for-unit root-unit 9 0 1 fn2-run-cache fn2-pool))
      ((mv hit-still & &) (fn2-run-cache-lookup root-unit root-alloc fn2-run-cache))
      ((mv sweep-code sweep-cnt fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-unpinned 0 (fn2-run-cache-rows fn2-run-cache) 9 0 1 fn2-run-cache fn2-pool))
      ((mv hit-after-sweep & &) (fn2-run-cache-lookup root-unit root-alloc fn2-run-cache))
      ((mv pin-rel & fn2-pool) (fn2-pool-query-release rslot0 rgen0 fn2-pool))
      ((mv sweep2-code sweep2-cnt fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-unpinned 0 (fn2-run-cache-rows fn2-run-cache) 9 0 1 fn2-run-cache fn2-pool))
      ((mv cold-start fn2-run-cursors)
       (fn2-run-cursor-start-cached 0 *fn2-sru-sid* top-level root-unit root-alloc
                                    *fn2-run-run-reader* 9 0 1 fn2-run-cursors fn2-run-cache))

      ;; 3. Negative controls: 1-bit payload corruption, wrong epoch, wrong page-kind.
      ((mv & bad-slot1 bad-gen1 fn2-run-cache fn2-pool)
       (fn2-sru-load-disk-page root-unit 100 disk 9 0 1 fn2-run-cache fn2-pool))
      ((mv bad1-code bad1-detail fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
       (fn2-run-page-reload root-unit root-epoch root-alloc 1 1 *page-kind-run-index*
                            0 900 950 bad-slot1 bad-gen1 190 9 0 1
                            fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((mv after-bad1 & &) (fn2-run-cache-lookup root-unit root-alloc fn2-run-cache))

      ((mv & bad-slot2 bad-gen2 fn2-run-cache fn2-pool)
       (fn2-sru-load-disk-page root-unit nil disk 9 0 1 fn2-run-cache fn2-pool))
      ((mv bad2-code & fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
       (fn2-run-page-reload root-unit 99 root-alloc 1 1 *page-kind-run-index*
                            0 900 950 bad-slot2 bad-gen2 190 9 0 1
                            fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((mv after-bad2 & &) (fn2-run-cache-lookup root-unit root-alloc fn2-run-cache))

      ((mv & bad-slot3 bad-gen3 fn2-run-cache fn2-pool)
       (fn2-sru-load-disk-page root-unit nil disk 9 0 1 fn2-run-cache fn2-pool))
      ((mv bad3-code bad3-detail fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool)
       (fn2-run-page-reload root-unit root-epoch root-alloc 1 1 *page-kind-run-data*
                            0 900 950 bad-slot3 bad-gen3 190 9 0 1
                            fn2-run-cache fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-fields fn2-pool))
      ((mv after-bad3 & &) (fn2-run-cache-lookup root-unit root-alloc fn2-run-cache))

      ;; Also test 1-bit corruption on a child leaf page during cursor :miss!
      ((mv & & fn2-fields fn2-pool)
       (fn2-run-load-values *fn2-overview-entry* (fn2-sru-nq 1 2) *fn2-run-run-query* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
      ((mv &
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-start-cursor-from-disk *fn2-sru-sid* top-level root-unit root-epoch root-alloc
                                       *page-kind-run-index* 190 disk
                                       fn2-extents fn2-run-page-writes fn2-run-installed
                                       fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                       fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv step-to-miss fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-sru-step-nonmore 16 nil fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((mv bad-miss-code bad-miss-detail
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-handle-miss 100 disk
                            fn2-extents fn2-run-page-writes fn2-run-installed
                            fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                            fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                            fn2-fc fn2-fc-context fn2-b3 fn2-digests))

      ;; 4. Authentic nonresident demand-paged lookups & cross-page scans on the 2-row cache!
      ((mv & & fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-unpinned 0 (fn2-run-cache-rows fn2-run-cache) 9 0 1 fn2-run-cache fn2-pool))
      ((mv paged-lookups
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-paged-lookups *fn2-sru-queries* *fn2-sru-sid* top-level root-unit root-epoch root-alloc 190
                              *fn2-overview-entry* qslot qgen disk
                              fn2-extents fn2-run-page-writes fn2-run-installed
                              fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                              fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                              fn2-fc fn2-fc-context fn2-b3 fn2-digests))

      ((mv & & fn2-fields fn2-pool)
       (fn2-run-load-values *fn2-overview-entry* (fn2-sru-nq 0 0) *fn2-run-run-query* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
      ((mv &
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-start-cursor-from-disk *fn2-sru-sid* top-level root-unit root-epoch root-alloc
                                       *page-kind-run-index* 190 disk
                                       fn2-extents fn2-run-page-writes fn2-run-installed
                                       fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                       fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv paged-scan-all
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-paged-scan-steps 500 20 (fn2-sru-nq 0 0) top-level root-unit root-epoch root-alloc 190 qslot qgen disk
                                 fn2-extents fn2-run-page-writes fn2-run-installed
                                 fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                 fn2-fc fn2-fc-context fn2-b3 fn2-digests))

      ;; 5. Live fn2-manifest (:id 10):
      ;; (a) Standalone pack -> truncated negative control -> authentic unpack.
      ((mv pack-code pack-len fn2-fields fn2-pool)
       (fn2-manifest-pack-entry 1200 mslot mgen *fn2-sru-sid* *fn2-sru-run-id* height entries-built
                                root-unit root-epoch root-alloc 190
                                nil 0 0 0 0
                                9 0 1 fn2-fields fn2-pool fn2-digests))
      ((mv trunc-unpack & & & & & & & & & & & fn2-fields fn2-digests)
       (fn2-manifest-unpack-entry 1220 mslot mgen (- pack-len 1) 191 192 9 0 1 fn2-fields fn2-pool fn2-digests))
      ((mv unpack-code u-sid u-run u-h u-ent u-ru u-rep u-ra u-fp & & & fn2-fields fn2-digests)
       (fn2-manifest-unpack-entry 1220 mslot mgen pack-len 191 192 9 0 1 fn2-fields fn2-pool fn2-digests))
      (unpack-hash-eq (fn2-digest-equal 190 191 fn2-digests))

      ;; (b) Build & seal an actual :manifest (sid=10, *page-kind-manifest*) run on fn2-extents!
      ((mv mstart fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-run-build-start 0 *fn2-manifest-sid* 1 0 0 136 hslot hgen 0 *fn2-run-page-size*
                            1 1 9 0 1 fn2-run-builds fn2-run-writers fn2-pool))
      ((mv mstage fn2-fields fn2-pool)
       (fn2-manifest-stage-entry *fn2-run-run-entry* src sgen 0
                                 *fn2-sru-sid* *fn2-sru-run-id* height entries-built
                                 root-unit root-epoch root-alloc 190
                                 nil 0 0 0 0
                                 9 0 1 fn2-fields fn2-pool fn2-digests))
      ((mv mneed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
       (fn2-run-build-add 0 *fn2-run-run-entry* fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv mpalloc & & & & & & fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
       (fn2-run-build-alloc-page 0 0 fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool))
      ((mv madd fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
       (fn2-run-build-add 0 *fn2-run-run-entry* fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv mfin fn2-run-builds) (fn2-run-build-finish 0 fn2-run-builds))
      ((mv mbuild-status mndesc disk
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-build-loop 10000 *fn2-manifest-entry* nil src sgen 0 ndesc nil disk
                           fn2-extents fn2-run-page-writes fn2-run-installed
                           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                           fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      (mroot-drow (- mndesc 1))
      (mroot-unit (fn2-run-page-writes-unit mroot-drow fn2-run-page-writes))
      (mroot-epoch (fn2-run-page-writes-epoch mroot-drow fn2-run-page-writes))
      (mroot-alloc (fn2-run-page-writes-allocation mroot-drow fn2-run-page-writes))
      (mroot-pkind (fn2-run-page-writes-page-kind mroot-drow fn2-run-page-writes))
      ((mv & fn2-digests)
       (fn2-run-page-write-extract-hash mroot-drow 193 fn2-run-page-writes fn2-digests))

      ;; Cold recovery: evict all pages from fn2-run-cache, reload :manifest root
      ;; from DISK, scan :manifest entry, reconstruct fn2-run-installed row 0 via
      ;; fn2-manifest-install-entry, then run cold lookup using fn2-run-installed!
      ((mv & & fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-unpinned 0 (fn2-run-cache-rows fn2-run-cache) 9 0 1 fn2-run-cache fn2-pool))
      (fn2-fields (fn2-fields-set-value (+ *fn2-run-run-query* *fn2-manifest-entry-field-schema*) 0 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ *fn2-run-run-query* *fn2-manifest-entry-field-run*) 0 fn2-fields))
      ((mv mstart-cur
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-start-cursor-from-disk *fn2-manifest-sid* 0 mroot-unit mroot-epoch mroot-alloc
                                       *page-kind-manifest* 193 disk
                                       fn2-extents fn2-run-page-writes fn2-run-installed
                                       fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                                       fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv mscan1 fn2-run-cursors fn2-run-paths fn2-fields)
       (fn2-sru-step-nonmore 16 t fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
      ((mv minstall fn2-digests fn2-run-installed)
       (fn2-manifest-install-entry 0 (+ *fn2-run-run-reader* *fn2-run-reader-entry*) 196 197
                                   0 0 9 0 1 fn2-fields fn2-pool fn2-digests fn2-run-installed))
      (rec-sid (fn2-run-installed-schema 0 fn2-run-installed))
      (rec-run (fn2-run-installed-run 0 fn2-run-installed))
      (rec-top (fn2-run-installed-top 0 fn2-run-installed))
      (rec-unit (fn2-run-installed-unit 0 fn2-run-installed))
      (rec-alloc (fn2-run-installed-counter 0 fn2-run-installed))
      (rec-entries (fn2-run-installed-entries 0 fn2-run-installed))
      ((mv recovered-lookups
           fn2-extents fn2-run-page-writes fn2-run-installed
           fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
           fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
           fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-sru-paged-lookups (list (fn2-sru-nq 1 14) (fn2-sru-nq 1 9))
                              rec-sid rec-top rec-unit *fn2-sru-epoch* rec-alloc 196
                              *fn2-overview-entry* qslot qgen disk
                              fn2-extents fn2-run-page-writes fn2-run-installed
                              fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                              fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                              fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
  (fn2-sru-mv
   (list :height height :ndesc ndesc :entries entries-built :desc-ok desc-ok :xh xh-code
         :pin (list hit0 pin-acq pinned-now evict-pinned hit-still
                    sweep-code (< 0 sweep-cnt) hit-after-sweep pin-rel sweep2-code sweep2-cnt cold-start)
         :neg (list bad1-code bad1-detail after-bad1
                    bad2-code after-bad2
                    bad3-code bad3-detail after-bad3
                    step-to-miss bad-miss-code bad-miss-detail)
         :lookups paged-lookups
         :scan paged-scan-all
         :manifest-pack (list pack-code trunc-unpack unpack-code
                              (list u-sid u-run u-h u-ent u-ru u-rep u-ra u-fp) unpack-hash-eq)
         :manifest-run (list mstart mstage mneed mpalloc madd mfin mbuild-status
                             (= mroot-pkind *page-kind-manifest*) mstart-cur mscan1 minstall
                             (list rec-sid rec-run rec-top rec-unit rec-alloc rec-entries)
                             recovered-lookups)))))

(defun fn2-sru-storage-result ()
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-extents fn2-run-page-writes fn2-run-installed
                      fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
                      fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
                      fn2-fc fn2-fc-context fn2-b3 fn2-digests)
  (fn2-sru-storage-scenario
   fn2-extents fn2-run-page-writes fn2-run-installed
   fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache
   fn2-run-writers fn2-run-restarts fn2-fields fn2-pool
   fn2-fc fn2-fc-context fn2-b3 fn2-digests)))

(defun fn2-sru-resident-lookups (qs)
 (declare (xargs :verify-guards nil :measure (len qs)))
 (if (atom qs)
     nil
   (cons (fn2-run-lookup-image *fn2-sru-sid* *fn2-overview-entry* *fn2-sru-entries-7* *fn2-sru-limit* (car qs))
         (fn2-sru-resident-lookups (cdr qs)))))

(assert-event
 (let ((res (fn2-sru-storage-result)))
  (and (equal (nth 1 res) 2)
       (equal (nth 3 res) 4)
       (equal (nth 5 res) 7)
       (equal (nth 7 res) t)
       (equal (nth 9 res) :ok)
       ;; Pin protection & unpinned eviction:
       (equal (nth 11 res) '(:ok :ok t :pinned :ok :ok t :ok :ok :ok 1 :miss))
       ;; Negative controls: 1-bit payload flip -> (:corrupt :bad-hash), cache :miss;
       ;; wrong epoch -> :corrupt, cache :miss; wrong page-kind -> (:corrupt :wrong-kind), cache :miss;
       ;; 1-bit child flip on cursor :miss -> (:corrupt :bad-hash).
       (equal (nth 13 res) '(:corrupt :bad-hash :miss
                             :corrupt :miss
                             :corrupt :wrong-kind :miss
                             :miss :corrupt :bad-hash))
       ;; Exact demand-paged lookup & scan equivalence against resident oracle:
       (equal (nth 15 res) (fn2-sru-resident-lookups *fn2-sru-queries*))
       (equal (nth 17 res)
              (fn2-run-scan-image *fn2-sru-sid* *fn2-overview-entry* *fn2-sru-entries-7* *fn2-sru-limit* (fn2-sru-nq 0 0) 20))
       ;; Standalone manifest pack/unpack + truncation refusal:
       (equal (car (nth 19 res)) :ok)
       (equal (cadr (nth 19 res)) :truncated)
       (equal (caddr (nth 19 res)) :ok)
       (equal (fifth (nth 19 res)) t)
       ;; Sealed :manifest run + cold fn2-run-installed reconstruction & cold lookup:
       (let ((mr (nth 21 res)))
        (and (equal (nth 0 mr) :ok)
             (equal (nth 1 mr) :ok)
             (equal (nth 2 mr) :need-page)
             (equal (nth 3 mr) :ok)
             (equal (nth 4 mr) :ok)
             (equal (nth 5 mr) :ok)
             (equal (car (nth 6 mr)) :root)
             (equal (nth 7 mr) t)
             (equal (nth 8 mr) :ok)
             (equal (nth 9 mr) :entry)
             (equal (nth 10 mr) :ok)
             (equal (car (nth 11 mr)) *fn2-sru-sid*)
             (equal (cadr (nth 11 mr)) *fn2-sru-run-id*)
             (equal (caddr (nth 11 mr)) 1)
             (equal (sixth (nth 11 mr)) 7)
             (equal (nth 12 mr)
                    (fn2-sru-resident-lookups (list (fn2-sru-nq 1 14) (fn2-sru-nq 1 9)))))))))

; ---------------------------------------------------------------------------
; Master Scenario 2: Productive Checkpoint Cut & Pin-Gated Extent Retirement
; (fn2-alloc-cut advances 0 -> 3 -> 4 -> 6, obligation & promised-read pins
; refuse reclamation, zero-pin drain frees extents, and subsequent reserve reuses!)

(defun fn2-sru-reclaim-scenario (fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
                 :verify-guards nil))
 (b* ((fn2-extents (fn2-alloc-init 2 fn2-extents))
      (fn2-alloc-edges (fn2-alloc-edges-init 8 fn2-alloc-edges))
      (fn2-retirement-control (fn2-retirement-control-init 1 fn2-retirement-control))
      (fn2-fields (fn2-fields-init 32 fn2-fields))
      (fn2-pool (fn2-pool-init '((2 . 256)) 1 50 fn2-pool))
      (cut0 (fn2-alloc-cut fn2-extents))
      ((mv & fn2-extents) (fn2-alloc-begin-epoch 2 fn2-extents))
      ((mv & & e0 ep0 c0 fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv & fn2-extents) (fn2-alloc-commit-allocation e0 ep0 c0 1 10 fn2-extents))
      ((mv & & e1 ep1 c1 fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv & fn2-extents) (fn2-alloc-commit-allocation e1 ep1 c1 1 11 fn2-extents))
      ;; Both extents allocated -> pool of 2 extents is now exhausted!
      ((mv exhausted-before & & & & fn2-extents) (fn2-alloc-reserve fn2-extents))
      ;; Pin extent 0 with :obligation.
      ((mv & fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-add 0 500 e0 ep0 c0 :obligation fn2-extents fn2-alloc-edges))
      ;; Advance checkpoint cut 0 -> 3 via fn2-checkpoint-cut-step.
      ((mv cut3-code fn2-extents) (fn2-checkpoint-cut-step 1 3 16 9 1 1 fn2-extents))
      (cut3 (fn2-alloc-cut fn2-extents))
      ;; Attempt to retire & reclaim extent 0 at retire-commit=3 while :obligation pin is active -> :obligation!
      ((mv pin-refuse1 fn2-extents fn2-retirement-control fn2-fields fn2-pool)
       (fn2-checkpoint-reclaim-step 2 3 16 e0 ep0 c0 3 1 0 9 1 1
                                    fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool))
      (st0-pinned (fn2-extents-state e0 fn2-extents))
      ;; Drop :obligation pin; advance cut -> 4 and reclaim extent 0!
      ((mv & fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-drop 0 500 e0 ep0 c0 :obligation fn2-extents fn2-alloc-edges))
      ((mv drain1-code drain1-cnt fn2-extents)
       (fn2-checkpoint-reclaim-drain-step 3 4 16 8 9 1 1 fn2-extents))
      (cut4 (fn2-alloc-cut fn2-extents))
      (st0-freed (fn2-extents-state e0 fn2-extents))
      ;; Submit & commit retirement of extent 1 at retire-commit=6 while cut=5 (< 6) -> :checkpoint-blocked!
      ((mv sub1 & & end1 fn2-extents fn2-retirement-control fn2-fields fn2-pool)
       (fn2-retirement-submit-children e1 ep1 c1 6 2 0 9 1 1 fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((mv com1 fn2-extents fn2-retirement-control fn2-fields fn2-pool)
       (fn2-retirement-commit-children 6 2 end1 0 9 1 1 fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((mv precut-drain precut-cnt fn2-extents)
       (fn2-checkpoint-reclaim-drain-step 4 5 16 8 9 1 1 fn2-extents))
      ;; Pin extent 1 with :promised-read, then advance cut -> 6 -> refuses :promised-read!
      ((mv & fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-add 1 600 e1 ep1 c1 :promised-read fn2-extents fn2-alloc-edges))
      ((mv pin-refuse2 & fn2-extents)
       (fn2-checkpoint-reclaim-drain-step 5 6 16 8 9 1 1 fn2-extents))
      (cut6 (fn2-alloc-cut fn2-extents))
      ;; Drop :promised-read pin -> drain reclaims extent 1 (:free), and reserve reuses reclaimed space!
      ((mv & fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-drop 1 600 e1 ep1 c1 :promised-read fn2-extents fn2-alloc-edges))
      ((mv drain2-code drain2-cnt fn2-extents)
       (fn2-checkpoint-reclaim-drain-step 6 6 16 8 9 1 1 fn2-extents))
      (st1-freed (fn2-extents-state e1 fn2-extents))
      ((mv reuse-code & reused-ext reuse-ep reuse-alloc fn2-extents)
       (fn2-alloc-reserve fn2-extents)))
  (mv (list :cuts (list cut0 cut3 cut4 cut6)
            :exhausted exhausted-before
            :cut3-code cut3-code
            :e0 (list pin-refuse1 (= st0-pinned *fn2-extent-state-retire-pending*) drain1-code drain1-cnt (= st0-freed *fn2-extent-state-free*))
            :e1 (list sub1 com1 precut-drain precut-cnt pin-refuse2 drain2-code drain2-cnt (= st1-freed *fn2-extent-state-free*))
            :reuse (list reuse-code (or (= reused-ext e0) (= reused-ext e1)) reuse-ep reuse-alloc))
      fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)))

(defun fn2-sru-reclaim-result ()
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
  (fn2-sru-reclaim-scenario fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)))

(assert-event
 (equal (fn2-sru-reclaim-result)
        '(:cuts (0 3 4 6)
          :exhausted :no-space
          :cut3-code :ok
          :e0 (:obligation t :ok 1 t)
          :e1 (:ok :ok :checkpoint-blocked 0 :promised-read :ok 1 t)
          :reuse (:ok t 2 2))))
